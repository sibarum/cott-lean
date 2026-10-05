import CottLean.T.Gaussian
import CottLean.T.Quadratic

/-!
# `C(C, C)`: a point with complex coordinates

The fourth corner. `C(T, T)` (`Point`) and `T(C, C)` (`RatioPoint`) both hold ℚ(i). Here both coordinates
are Gaussian integers and the pair is read as a point, `B + A·j`. There are two square roots of `−1` now:
the `i` inside each coordinate and the `j` of the point. With `j² = −1` this is
`QuadraticAlgebra ℤ[i] (−1) 0`, the bicomplex integers (`toQuad`, a ring isomorphism).

## Two units, not one

* `ofInner` puts a flat point on the inner `i`: `T(p, q) ↦ C(0, q + p·i)`. `ofOuter` puts it on the
  outer `j`: `T(p, q) ↦ C(p, q)`. Both carry `⊕` and `⊗` exactly (`ofInner_otimes`, `ofOuter_otimes`), and
  they differ (`inner_ne_outer`).
* `i·j` squares to `+1` (`ij_sq`). So `C(C, C)` has zero divisors, `(1 + ij)(1 − ij) = 0`
  (`zero_divisors`). It is the first corner of the grid that is not a domain.
* And it holds the split-complex product: `T(p, q) ↦ C(p·i, q)` carries `⊚` to `⊗` exactly
  (`ofSplit_otimes`). Angle addition (`⊗`, through `ofOuter`) and velocity addition (`⊚`, through
  `ofSplit`) are one product here.

## One `i` collapses

`evPlus` reads `j` as `i`, `B + i·A`, and `evMinus` reads it as `−i`, `B − i·A`. Each is a ring map to
`ℤ[i]` (`evPlus_otimes`, `evMinus_otimes`).

* `evPlus_inner_eq_outer`: under `evPlus` the two placements of a flat point agree. Identifying `j` with
  `i` is exactly what loses the distinction, and `evPlus` is not injective (`evPlus_not_injective`).
* `ev_injective`: the two evaluations together lose nothing.
* `ev_not_surjective`: but they do not reach every pair. `(1, 0)` would need `2B = 1`. Over ℤ the
  bicomplex integers are not `ℤ[i] × ℤ[i]`, as the split-complex integers are not `ℤ × ℤ`
  (`T.split_not_prod`). The two agree once `2` is invertible.

## The norm, which is complex

`nrm z = B² + A²`, a Gaussian integer, and it is `evPlus z · evMinus z` (`nrm_eq_ev_mul`). It is what
`z ⊗ conj z` leaves, with `conj` turning `j` (`otimes_conj`).

* `otimes_cancel_iff`: `⊗ k` can be undone exactly when `nrm k ≠ 0`.
* `nrm_eq_zero_iff`: and `nrm k = 0` exactly on the two light lines `B = ±i·A`.
* Read through each flat placement, the norm is that product's own norm: `p² + q²` for `⊗`
  (`nrm_ofOuter`), `q² − p²` for `⊚` (`nrm_ofSplit`), and the square `(q + p·i)²` on the inner unit
  (`nrm_ofInner`).

An exact inverse is `(B − A·j) / nrm`, and `nrm` is a Gaussian integer, so it needs coordinates that are
ratios of Gaussian integers, `C(T(C, C), T(C, C))` (`BicomplexRatio`). Even there it fails on the light
lines, where `nrm` is zero and the point is not.
-/

open T

/-- `C(C, C)`: the point `B + A·j`, with `A` and `B` Gaussian integers. -/
@[ext]
structure CC where
  /-- The `j` coordinate. -/
  p : GaussianInt
  /-- The real coordinate. -/
  q : GaussianInt
  deriving DecidableEq

namespace CC

/-- The Gaussian unit `i`, inside a coordinate. -/
def gi : GaussianInt := ⟨0, 1⟩

theorem gi_mul_gi : gi * gi = -1 := by decide

/-! ## The operations -/

/-- The sum of the points. -/
def oplus (x y : CC) : CC := ⟨x.p + y.p, x.q + y.q⟩

/-- The product of the points, with `j² = −1`. -/
def otimes (x y : CC) : CC := ⟨x.p * y.q + y.p * x.q, x.q * y.q - x.p * y.p⟩

/-- `B + A·j ↦ B − A·j`: `j` turned, `i` left alone. -/
def conj (x : CC) : CC := ⟨-x.p, x.q⟩

/-- `C(C, C)` is `QuadraticAlgebra ℤ[i] (−1) 0`. -/
def toQuad : CC ≃ QuadraticAlgebra GaussianInt (-1) 0 where
  toFun x := ⟨x.q, x.p⟩
  invFun z := ⟨z.im, z.re⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toQuad_oplus (x y : CC) : toQuad (oplus x y) = toQuad x + toQuad y := by
  ext <;> simp [toQuad, oplus]

theorem toQuad_otimes (x y : CC) : toQuad (otimes x y) = toQuad x * toQuad y := by
  ext <;> simp [toQuad, otimes] <;> ring

/-! ## Two placements of a flat point, and the split-complex one -/

/-- A flat point on the inner unit: `T(p, q) ↦ C(0, q + p·i)`. -/
def ofInner (z : T) : CC := ⟨0, toGaussian z⟩

/-- A flat point on the outer unit: `T(p, q) ↦ C(p, q)`. -/
def ofOuter (z : T) : CC := ⟨z.p, z.q⟩

/-- A flat split-complex point: `T(p, q) ↦ C(p·i, q)`, so `ω ↦ i·j`. -/
def ofSplit (z : T) : CC := ⟨z.p * gi, z.q⟩

theorem ofInner_oplus (x y : T) : ofInner (x ⊕ y) = oplus (ofInner x) (ofInner y) := by
  ext <;> simp [ofInner, oplus, toGaussian_oplus]

theorem ofInner_otimes (x y : T) : ofInner (x ⊗ y) = otimes (ofInner x) (ofInner y) := by
  ext <;> simp [ofInner, otimes, toGaussian_otimes]

theorem ofOuter_oplus (x y : T) : ofOuter (x ⊕ y) = oplus (ofOuter x) (ofOuter y) := by
  ext <;> simp [ofOuter, oplus, T.oplus]

theorem ofOuter_otimes (x y : T) : ofOuter (x ⊗ y) = otimes (ofOuter x) (ofOuter y) := by
  ext <;> simp [ofOuter, otimes, T.otimes]

theorem ofSplit_otimes (x y : T) : ofSplit (x ⊚ y) = otimes (ofSplit x) (ofSplit y) := by
  have h := gi_mul_gi
  ext1
  · simp [ofSplit, otimes, splitTimes, qtimes]; ring
  · simp only [ofSplit, otimes, splitTimes, qtimes]; push_cast
    linear_combination ((x.p : GaussianInt) * y.p) * h

/-- `i` and `j` are different units: the flat `ω` lands on different points. -/
theorem inner_ne_outer : ofInner «ω» ≠ ofOuter «ω» := by decide

/-- `(i·j)² = 1`. -/
theorem ij_sq : otimes ⟨gi, 0⟩ ⟨gi, 0⟩ = ⟨0, 1⟩ := by decide

/-- `(1 + ij)(1 − ij) = 0`, and neither factor is `0`. -/
theorem zero_divisors :
    otimes ⟨gi, 1⟩ ⟨-gi, 1⟩ = ⟨0, 0⟩ ∧ (⟨gi, 1⟩ : CC) ≠ ⟨0, 0⟩ ∧ (⟨-gi, 1⟩ : CC) ≠ ⟨0, 0⟩ := by
  decide

/-! ## Reading `j` as `±i` -/

/-- `j ↦ i`. -/
def evPlus (x : CC) : GaussianInt := x.q + gi * x.p

/-- `j ↦ −i`. -/
def evMinus (x : CC) : GaussianInt := x.q - gi * x.p

theorem evPlus_oplus (x y : CC) : evPlus (oplus x y) = evPlus x + evPlus y := by
  simp only [evPlus, oplus]; ring

theorem evMinus_oplus (x y : CC) : evMinus (oplus x y) = evMinus x + evMinus y := by
  simp only [evMinus, oplus]; ring

theorem evPlus_otimes (x y : CC) : evPlus (otimes x y) = evPlus x * evPlus y := by
  simp only [evPlus, otimes]; linear_combination (-(x.p * y.p)) * gi_mul_gi

theorem evMinus_otimes (x y : CC) : evMinus (otimes x y) = evMinus x * evMinus y := by
  simp only [evMinus, otimes]; linear_combination (-(x.p * y.p)) * gi_mul_gi

/-- With `j` read as `i`, the inner and outer placements of a flat point coincide. -/
theorem evPlus_inner_eq_outer (z : T) : evPlus (ofInner z) = evPlus (ofOuter z) := by
  apply Zsqrtd.ext <;> simp [evPlus, ofInner, ofOuter, gi, toGaussian, Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem evPlus_not_injective : ¬ Function.Injective evPlus := by
  intro h
  have := h (a₁ := ofInner «ω») (a₂ := ofOuter «ω») (evPlus_inner_eq_outer _)
  exact inner_ne_outer this

/-- The two evaluations together lose nothing. -/
theorem ev_injective {x y : CC} (h₁ : evPlus x = evPlus y) (h₂ : evMinus x = evMinus y) : x = y := by
  simp only [evPlus, evMinus] at h₁ h₂
  have hp : (2 * gi) * (x.p - y.p) = 0 := by linear_combination h₁ - h₂
  have h2gi : (2 * gi : GaussianInt) ≠ 0 := by decide
  have hp' : x.p = y.p := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left h2gi)
  ext1
  · exact hp'
  · rw [hp'] at h₁; linear_combination h₁

/-- But they do not reach `(1, 0)`: that would need `2B = 1`. -/
theorem ev_not_surjective : ¬ ∃ x : CC, evPlus x = 1 ∧ evMinus x = 0 := by
  rintro ⟨x, h₁, h₂⟩
  simp only [evPlus, evMinus] at h₁ h₂
  have h : 2 * x.q = 1 := by linear_combination h₁ + h₂
  have := congrArg Zsqrtd.re h
  simp [Zsqrtd.re_mul] at this
  omega

/-! ## The norm -/

/-- `B² + A²`, a Gaussian integer. -/
def nrm (x : CC) : GaussianInt := x.q ^ 2 + x.p ^ 2

theorem nrm_eq_ev_mul (x : CC) : nrm x = evPlus x * evMinus x := by
  simp only [nrm, evPlus, evMinus]; linear_combination (x.p ^ 2) * gi_mul_gi

/-- `z ⊗ conj z` is the norm, left standing in the real coordinate. -/
theorem otimes_conj (x : CC) : otimes x (conj x) = ⟨0, nrm x⟩ := by
  ext1 <;> simp only [otimes, conj, nrm] <;> ring

/-- `nrm k = 0` exactly on the light lines `B = ±i·A`. -/
theorem nrm_eq_zero_iff (k : CC) : nrm k = 0 ↔ k.q = -(gi * k.p) ∨ k.q = gi * k.p := by
  rw [nrm_eq_ev_mul, mul_eq_zero, evPlus, evMinus, add_eq_zero_iff_eq_neg, sub_eq_zero]

/-- `⊗ k` can be undone exactly when the norm of `k` is not zero. -/
theorem otimes_cancel_iff (k : CC) :
    (∀ x x' : CC, otimes x k = otimes x' k → x = x') ↔ nrm k ≠ 0 := by
  rw [nrm_eq_ev_mul]
  constructor
  · intro h hk
    rcases mul_eq_zero.mp hk with hk | hk
    · -- `⟨1, i⟩` is killed by `evMinus`, so against `k` it lands where `0` does.
      have := h ⟨1, gi⟩ ⟨0, 0⟩ (ev_injective
        (by rw [evPlus_otimes, evPlus_otimes, hk]; ring)
        (by rw [evMinus_otimes, evMinus_otimes]; simp [evMinus]))
      exact absurd this (by decide)
    · have := h ⟨1, -gi⟩ ⟨0, 0⟩ (ev_injective
        (by rw [evPlus_otimes, evPlus_otimes]; simp [evPlus])
        (by rw [evMinus_otimes, evMinus_otimes, hk]; ring))
      exact absurd this (by decide)
  · intro hk x x' h
    have h₁ := congrArg evPlus h
    have h₂ := congrArg evMinus h
    rw [evPlus_otimes, evPlus_otimes] at h₁
    rw [evMinus_otimes, evMinus_otimes] at h₂
    exact ev_injective (mul_right_cancel₀ (left_ne_zero_of_mul hk) h₁)
      (mul_right_cancel₀ (right_ne_zero_of_mul hk) h₂)

/-- Through the outer placement the norm is `⊗`'s, `p² + q²`. -/
theorem nrm_ofOuter (z : T) : nrm (ofOuter z) = ((z.p ^ 2 + z.q ^ 2 : ℤ) : GaussianInt) := by
  simp only [nrm, ofOuter]; push_cast; ring

/-- Through the split placement it is `⊚`'s, `q² − p²`: the light lines. -/
theorem nrm_ofSplit (z : T) : nrm (ofSplit z) = ((z.q ^ 2 - z.p ^ 2 : ℤ) : GaussianInt) := by
  simp only [nrm, ofSplit]; push_cast; linear_combination ((z.p : GaussianInt) ^ 2) * gi_mul_gi

/-- On the inner unit it is the square of the Gaussian integer. -/
theorem nrm_ofInner (z : T) : nrm (ofInner z) = toGaussian z ^ 2 := by
  simp [nrm, ofInner]

end CC
